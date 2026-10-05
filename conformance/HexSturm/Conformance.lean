/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Transport
public import HexSturm.Reduced
public meta import HexSturm.Transport
public import HexSturm.Fixtures
public import HexRealRoots.TarskiTests
public meta import HexSturm.Basic
public meta import HexSturm.Fixtures
public meta import HexRealRoots.TarskiTests
public meta import HexPolyZ.IntegerPolynomial

public section

/-!
Oracle: none for HexSturm-owned code; differential checks against
`ZPoly.tarskiQuery`, whose integer fixtures are checked by pinned python-flint
in `conformance/HexRealRoots`.
Mode: always (core); required (HexRealRoots oracle on its owning PRs and on main).
A HexSturm-only PR does not select that oracle. This module elaborates through
`HexConformance`; field/integer differential checks supplement analytic expectations.
Covered operations:
- Preparation, positive normalization and endpoint retargeting.
- Ordinary/prepared queries, counts and certification.
- Cached/plain checking and literal step/chain/certificate denominator clearing and embedding.
Covered properties:
- Analytic counts and sign sums for ±1 and the eight Chebyshev roots.
- Prepared-chain reuse, exact input/context binding and positive scaling agreement.
Covered edge cases:
- Constants, zero/repeated heads and common query roots.
- Invalid/equal/reversed bounds and all finite/infinite endpoint pairs.
- Noncanonical coefficients, corrupted identities, stale endpoints and foreign contexts.
Differential checks are not an independent semantic oracle.
-/
namespace Hex.Sturm.Conformance

open DensePoly Hex.Sturm.Fixtures
open scoped Hex


#guard rootCount orderSign p .negInf .posInf == some 2
#guard rootCount orderSign p (.finite 0) .posInf == some 1
#guard rootCount orderSign p .negInf (.finite 0) == some 1
#guard rootCount orderSign (C 5 : DensePoly Rat) .negInf .posInf == some 0
#guard rootCount orderSign (0 : DensePoly Rat) .negInf .posInf == none
#guard rootCount orderSign (natPow (x - 1) 2) .negInf .posInf == none
#guard rootCount orderSign p (.finite 1) .posInf == none
#guard rootCount orderSign p (.finite 2) (.finite (-2)) == none

#guard query orderSign p 1 .negInf .posInf == some 2
#guard query orderSign p (C (-1)) .negInf .posInf == some (-2)
#guard query orderSign p 0 .negInf .posInf == some 0
#guard query orderSign p x .negInf .posInf == some 0
#guard query orderSign p (x - 1) .negInf .posInf == some (-1)
#guard query orderSign p (natPow x 8) .negInf .posInf == some 2
#guard query orderSign p p .negInf .posInf == some 0
#guard query orderSign (-p) 1 .negInf .posInf == some 2
#guard query orderSign (scale 4 x) 1 .negInf .posInf == some 1
#guard query orderSign (C 5 : DensePoly Rat) 0 .negInf .posInf == some 0
#guard query orderSign (0 : DensePoly Rat) 0 .negInf .posInf == none
#guard query orderSign (natPow (x - 1) 2) 0 .negInf .posInf == none
#guard query orderSign p 0 .negInf .negInf == none
#guard query orderSign p 0 .posInf .posInf == none
#guard query orderSign p 0 .posInf .negInf == none
#guard query orderSign p 0 (.finite 0) .negInf == none
#guard query orderSign p 0 .posInf (.finite 0) == none
#guard query orderSign p 0 (.finite 0) (.finite 0) == none
#guard query orderSign p 0 (.finite 2) (.finite (-2)) == none
#guard query orderSign p 0 (.finite (-1)) .posInf == none
#guard query orderSign p 0 .negInf (.finite 1) == none
#guard query orderSign p 1 .negInf (.finite 0) == some 1
#guard query orderSign p 1 (.finite 0) .posInf == some 1
#guard query orderSign p x .negInf (.finite 0) == some (-1)
#guard query orderSign p x (.finite 0) .posInf == some 1

#guard match prepare orderSign p .negInf .posInf with
  | none => false
  | some domain => queryPrepared domain 1 == 2 && queryPrepared domain x == 0 &&
    queryPrepared domain (x - 1) == -1 &&
    check orderSign (7 : Nat) p (x - 1) .negInf .posInf (-1)
      (certifyPrepared 7 domain (x - 1)) &&
    !check orderSign (8 : Nat) p (x - 1) .negInf .posInf (-1)
      (certifyPrepared 7 domain (x - 1))

#guard match certify orderSign (7 : Nat) p (x - 1) .negInf .posInf with
  | none => false
  | some cert => check orderSign 7 p (x - 1) .negInf .posInf (-1) cert &&
    !check orderSign 8 p (x - 1) .negInf .posInf (-1) cert &&
    !check orderSign 7 p (x - 1) (.finite 0) .posInf (-1) cert

/- T_8 has eight simple roots cos((2k−1)π/16), all strictly between ±1.
This degree-eight irrational-root head exercises a multi-step chain. Symmetry
makes the X sign sum zero; no root is zero, so the X² sign sum is eight. -/
#guard
  let head : DensePoly Rat := ofCoeffs #[1, 0, -32, 0, 160, 0, -256, 0, 128]
  match prepare orderSign head (.finite (-2)) (.finite 2) with
  | none => false
  | some domain =>
    countPrepared domain == 8 && domain.squarefree.steps.size > 1 &&
    (#[ (1, 8), (x, 0), (x * x, 8)] : Array (DensePoly Rat × Int)).all
      fun (f, expected) =>
        queryPrepared domain f == expected &&
          query orderSign head f .negInf .posInf == some expected &&
          check orderSign (7 : Nat) head f (.finite (-2)) (.finite 2) expected
            (certifyPrepared 7 domain f)

/- Normalization retains the leading sign and reconstructs the original head.
These exact cases include a negative leading coefficient and rational scale. -/
#guard (#[((ofCoeffs #[-2, 0, 2] : DensePoly Rat), 2, ofCoeffs #[-1, 0, 1]),
    (ofCoeffs #[-2, 0, -2], 2, ofCoeffs #[-1, 0, -1]),
    (ofCoeffs #[3 / 2, -3 / 2], 3 / 2, ofCoeffs #[1, -1]),
    (C 5, 5, C 1), (0, 0, 0)] : Array (DensePoly Rat × Rat × DensePoly Rat)).all
  fun (head, factor, normalized) =>
    normalize orderSign head == (factor, normalized) && scale factor normalized == head

/- Valid cache hits, absent caches and foreign-domain misses agree on three
independent analytic queries. Cached evidence must never accept corrupt query
identities, a foreign context, or stale endpoint bindings. -/
#guard match certify orderSign (7 : Nat) p 1 .negInf .posInf with
  | none => false
  | some parent =>
    let cache := TarskiCertificate.Domain.replay? orderSign
      (EndpointSigns.ofSign orderSign) parent.domain
    cache.isSome && (#[ (1, 2), (x, 0), (x - 1, -1)] :
        Array (DensePoly Rat × Int)).all fun (f, expected) =>
      match certify orderSign (7 : Nat) p f .negInf .posInf,
          certify orderSign (8 : Nat) p f .negInf .posInf with
      | some cert, some foreign =>
        let foreignCache := TarskiCertificate.Domain.replay? orderSign
          (EndpointSigns.ofSign orderSign) foreign.domain
        let corrupt := { cert with remainders :=
          { cert.remainders with initial := ⟨1, 1, 2⟩ } }
        foreignCache.isSome &&
          checkCached orderSign 7 p f .negInf .posInf expected cache cert &&
          checkCached orderSign 7 p f .negInf .posInf expected none cert &&
          checkCached orderSign 7 p f .negInf .posInf expected foreignCache cert &&
          !checkCached orderSign 8 p f .negInf .posInf expected cache cert &&
          !checkCached orderSign 7 p f (.finite 0) .posInf expected cache cert &&
          !checkCached orderSign 7 p f .negInf .posInf expected cache corrupt
      | _, _ => false

/- Endpoint retargeting checks every finite/infinite pair, including root
endpoints and reversed bounds. The count oracle evaluates the two known roots
against the requested open interval, independently of remainder chains. -/
#guard match prepare orderSign p .negInf .posInf with
  | none => false
  | some domain =>
    let bounds : Array (Endpoint Rat) :=
      #[.negInf, .finite (-2), .finite (-1), .finite 0, .finite 1, .finite 2, .posInf]
    bounds.all fun a => bounds.all fun b =>
      let retargeted := domain.withEndpoints? a b
      (retargeted.map countPrepared == query orderSign p 1 a b) &&
      match retargeted with
      | none => !TarskiCertificate.checkEndpoints (EndpointSigns.ofSign orderSign) p a b
      | some next =>
        let expected := (#[-1, 1] : Array Rat).filter fun root =>
          a.lt (EndpointSigns.ofSign orderSign) (.finite root) &&
          (Endpoint.finite root).lt (EndpointSigns.ofSign orderSign) b
        next.head == domain.head && next.squarefree == domain.squarefree &&
          next.lower == a && next.upper == b && countPrepared next == (expected.size : Int)

/- Each side receives fresh endpoint signs and literal certificates. A
parent certificate or a foreign context cannot stand in for the child. -/
#guard match prepare orderSign p .negInf .posInf with
  | none => false
  | some domain => match domain.withEndpoints? .negInf (.finite 0),
      domain.withEndpoints? (.finite 0) .posInf with
    | some left, some right =>
      let parent := certifyCountPrepared (7 : Nat) domain
      let child := certifyCountPrepared (7 : Nat) left
      let forged := { parent with upper := .finite 0, value := 1 }
      let staleSigns := { parent with upper := .finite 0 }
      countPrepared domain == 2 && countPrepared left == 1 && countPrepared right == 1 &&
      check orderSign 7 p 1 .negInf (.finite 0) 1 child &&
      !check orderSign 8 p 1 .negInf (.finite 0) 1 child &&
      !check orderSign 7 p 1 .negInf (.finite 0) 1 parent &&
      !check orderSign 7 p 1 .negInf (.finite 0) 1 forged &&
      !check orderSign 7 p 1 .negInf (.finite 0) 2 staleSigns &&
      !check orderSign 7 p 1 .negInf .posInf 2 child
    | _, _ => false

#guard (#[(-p, 2), (x * x + 1, 0), (C 5, 0)] : Array (DensePoly Rat × Int)).all fun (head, count) =>
  match prepare orderSign head .negInf .posInf with
  | none => false
  | some domain => countPrepared domain == count &&
    check orderSign (7 : Nat) head 1 .negInf .posInf count (certifyCountPrepared 7 domain) &&
    match domain.withEndpoints? (.finite (-2)) (.finite 2) with
    | none => false
    | some next => countPrepared next == count

/- Storage has no field instance and is genuinely noncanonical. -/
#guard match prepare Hex.TarskiTests.Noncanonical.sign Hex.TarskiTests.Noncanonical.head
    .negInf .posInf with
  | none => false
  | some domain => match domain.withEndpoints? (.finite 0) .posInf with
    | none => false
    | some next => countPrepared domain == 2 && countPrepared next == 1 &&
      check Hex.TarskiTests.Noncanonical.sign (7 : Nat) Hex.TarskiTests.Noncanonical.head 1
        (.finite 0) .posInf 1
        (certifyCountPrepared 7 next)

/- Positive independent denominator clearing preserves complete runtime
results, including the `none` cases and zero query polynomials. -/
#guard (#[0, C 5, Hex.TarskiTests.p, -Hex.TarskiTests.p,
    natPow Hex.TarskiTests.x 2, scale 4 Hex.TarskiTests.x] : Array ZPoly).all fun pz =>
  (#[0, 1, C (-1), Hex.TarskiTests.x, Hex.TarskiTests.x - 1,
    natPow Hex.TarskiTests.x 8] : Array ZPoly).all fun fz =>
    let pr := scale (1 / 6 : Rat) (ZPoly.toRatPoly pz)
    let fr := scale (1 / 10 : Rat) (ZPoly.toRatPoly fz)
    let cp := ZPoly.clearDenominators pr
    let cf := ZPoly.clearDenominators fr
    0 < cp.1 && 0 < cf.1 &&
      query orderSign pr fr (.finite (-2)) (.finite 2) ==
        ZPoly.tarskiQuery cp.2 cf.2 Hex.TarskiTests.interval &&
      query orderSign pr fr (.finite (-2)) (.finite 2) ==
        ZPoly.tarskiQuery pz fz Hex.TarskiTests.interval

/- Negative clearing of the query changes its sign and is not admissible denominator clearing. -/
#guard query orderSign (scale (1 / 6 : Rat) p) (C (-1 / 10)) .negInf .posInf == some (-2)

/- The same frontend accepts noncanonical arithmetic without a field instance. -/
#guard query Hex.TarskiTests.Noncanonical.sign Hex.TarskiTests.Noncanonical.head 1
  .negInf .posInf == some 2

/- Squarefreeness evidence is checked independently of the query chain. -/
#guard !check orderSign 7 p 1 (.finite (-2)) (.finite 2) 2
  { literal with squarefree := { literalChain with terminal := some (1, 1) } }

/- A constant tail alone cannot certify a repeated-root head. -/
#guard !check orderSign 7 (natPow (x - 1) 2) 1 (.finite (-2)) (.finite 2) 2
  { literal with
    head := natPow (x - 1) 2
    squarefree := { literalChain with chain := #[natPow (x - 1) 2, x - 1, 1] }
    remainders := { literalChain with chain := #[natPow (x - 1) 2, x - 1, 1] } }

/- Positive scales do not excuse a false initial reduction identity. -/
#guard !check orderSign 7 p 1 (.finite (-2)) (.finite 2) 2
  { literal with remainders := { literalChain with initial := ⟨1, 1, 2⟩ } }

/- A genuine repeated-root chain passes all identities but has a nonconstant
terminal gcd. The squarefree constant-tail guard must reject it. -/
#guard
  let chain : SignedRemainderChain Rat :=
    { chain := #[x * x, x], degrees := #[2, 1], initial := ⟨1, 0, 2⟩,
      steps := #[], terminal := some (1, x) }
  SignedRemainderChain.check orderSign (x * x) 1 chain && !SignedRemainderChain.lastIsConstant chain &&
    !check orderSign 7 (x * x) 1 (.finite (-2)) (.finite 2) 1
      { literal with
        head := x * x
        squarefree := chain
        remainders := chain
        lowerSigns := #[1, -1]
        upperSigns := #[1, 1]
        lowerVariations := 1
        value := 1 }

theorem literal_checks : check orderSign 7 p 1 (.finite (-2)) (.finite 2) 2 literal = true := by
  simp only [check, TarskiCertificate.check_eq, SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

theorem stale_rejected : check orderSign 8 p 1 (.finite (-2)) (.finite 2) 2 literal = false := by
  decide +kernel

/-- info: 'Hex.Sturm.Conformance.literal_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_checks
/-- info: 'Hex.Sturm.Conformance.stale_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stale_rejected

/-- info: 'Hex.Sturm.prepare_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Sturm.prepare_eq_some
/-- info: 'Hex.Sturm.certifyPrepared_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Sturm.certifyPrepared_value
/-- info: 'Hex.Sturm.certify_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Sturm.certify_value
/-- info: 'Hex.Sturm.check_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Sturm.check_bindings

/-- info: 'Hex.Sturm.query_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Sturm.query_prepared
/-- info: 'Hex.Sturm.certify_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Sturm.certify_prepared
/-- info: 'Hex.Sturm.prepare_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Sturm.prepare_isSome

/- Three analytically specified identities a*A = q*B − c*C, including
coprime denominators. Translate the literal step itself and reject an incorrect
right scale in both domains; neither test invokes a chain producer. -/
#guard (#[ (1, 1, 1), (6, 10, 15), (997, 991, 983)] : Array (Nat × Nat × Nat)).all
  fun (a, b, c) =>
    let A := scale (1 / (a : Rat)) p
    let B := scale (1 / (b : Rat)) x
    let C := DensePoly.C (1 / (c : Rat))
    let step : RemainderStep Rat := ⟨a, scale (b : Rat) x, c⟩
    let ca := ZPoly.clearDenominators A
    let cb := ZPoly.clearDenominators B
    let cc := ZPoly.clearDenominators C
    let cleared := step.clearDenominators ca.1 cb.1 cc.1
    let wrong := { step with rightScale := (c : Rat) + 1 }
    SignedRemainderChain.checkStep orderSign A B C step &&
      SignedRemainderChain.checkStep Int.sign ca.2 cb.2 cc.2 cleared &&
      !SignedRemainderChain.checkStep orderSign A B C wrong &&
      !SignedRemainderChain.checkStep Int.sign ca.2 cb.2 cc.2
        (wrong.clearDenominators ca.1 cb.1 cc.1)

/- Transport exercises singleton chains, proper common factors and constants.
Each translated certificate is checked independently, including wrong bindings. -/
#guard (#[0, p, x - 1, 1] : Array (DensePoly Rat)).all fun f =>
  let p := scale (1 / 6 : Rat) p
  let f := scale (1 / 10 : Rat) f
  match certify orderSign (7 : Nat) p f (.finite (-2)) (.finite 2) with
  | none => false
  | some c =>
    let z := c.clearDenominators p f Hex.TarskiTests.interval
    let zp := (ZPoly.clearDenominators p).2
    let cf := ZPoly.clearDenominators f
    let zf := cf.2
    let a := Endpoint.finite Hex.TarskiTests.interval.lower
    let b := Endpoint.finite Hex.TarskiTests.interval.upper
    SignedRemainderChain.check Int.sign zp zf
        (c.remainders.clearDenominators p cf.1) &&
      TarskiCertificate.check Int.sign EndpointSigns.intDyadic 7 zp zf a b c.value z &&
      !TarskiCertificate.check Int.sign EndpointSigns.intDyadic 8 zp zf a b c.value z &&
      !TarskiCertificate.check Int.sign EndpointSigns.intDyadic 7 zp zf a b (c.value + 1) z &&
      !TarskiCertificate.check Int.sign EndpointSigns.intDyadic 7 zp zf b a c.value z &&
      !TarskiCertificate.check Int.sign EndpointSigns.intDyadic 7 zp zf a b c.value
        { z with remainders := { z.remainders with
          initial := { z.remainders.initial with leftScale := -z.remainders.initial.leftScale } } } &&
      check orderSign 7 (ZPoly.toRatPoly zp) (ZPoly.toRatPoly zf)
        (.finite (-2)) (.finite 2) c.value z.toRat

#guard match TarskiCertificate.certify Int.sign EndpointSigns.intDyadic ZPoly.normalizeContent
    (7 : Nat) Hex.TarskiTests.p (Hex.TarskiTests.x - 1) .negInf .posInf with
  | none => false
  | some c => check orderSign 7 p (x - 1) .negInf .posInf (-1) c.toRat

private def reducedCases : Array
    (DensePoly Rat × DensePoly Rat × Endpoint Rat × Endpoint Rat × Option Int) :=
  let head : DensePoly Rat := DensePoly.ofCoeffs #[-2, 0, 1]
  let wide := DensePoly.monomial 64 (1 : Rat) + 1
  #[(head, wide, .finite (-2), .finite 2, some 2),
    (head, -1, .negInf, .posInf, some (-2)),
    (head, 0, .negInf, .posInf, some 0),
    (head, head, .negInf, .posInf, some 0),
    (head, DensePoly.monomial 1 1, .negInf, .posInf, some 0),
    (head, wide, .finite 2, .finite 3, some 0),
    (DensePoly.ofCoeffs #[4, 0, -2], wide, .negInf, .posInf, some 2),
    (1, wide, .negInf, .posInf, some 0),
    (0, wide, .negInf, .posInf, none),
    (DensePoly.ofCoeffs #[1, -2, 1], wide, .negInf, .posInf, none),
    (DensePoly.ofCoeffs #[-1, 0, 1], wide, .finite (-1), .finite 2, none),
    (head, wide, .finite 2, .finite (-2), none)]

#guard reducedCases.all fun (p, q, a, b, expected) =>
  queryReduced orderSign p q a b == expected && query orderSign p q a b == expected

#guard match prepare orderSign (DensePoly.ofCoeffs #[-2, 0, (1 : Rat)])
    (.finite (-2)) (.finite 2) with
  | none => false
  | some domain =>
      let q := DensePoly.monomial 64 (1 : Rat) + 1
      queryReducedPrepared domain q == 2 && queryPrepared domain q == 2

end Hex.Sturm.Conformance
