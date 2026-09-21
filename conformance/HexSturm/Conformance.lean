/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Fixtures
public import HexRealRoots.QueryTests
public meta import HexSturm.Basic
public meta import HexSturm.Fixtures
public meta import HexRealRoots.QueryTests
public meta import HexPolyZ.IntegerPolynomial

public section

/-! Field frontend conformance: infinities, invalid domains, prepared reuse,
literal context bindings and positive rational/integer scaling agreement.
Computational conformance owner: `HexSturm`.
The rational/integer comparisons are runtime validation, not a backend theorem. -/
namespace Hex.Sturm.Conformance

open DensePoly Hex.Sturm.Fixtures
open scoped Hex


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
    Replay.check orderSign (7 : Nat) p (x - 1) .negInf .posInf (-1)
      (certifyPrepared 7 domain (x - 1)) &&
    !Replay.check orderSign (8 : Nat) p (x - 1) .negInf .posInf (-1)
      (certifyPrepared 7 domain (x - 1))

#guard match certify orderSign (7 : Nat) p (x - 1) .negInf .posInf with
  | none => false
  | some cert => Replay.check orderSign 7 p (x - 1) .negInf .posInf (-1) cert &&
    !Replay.check orderSign 8 p (x - 1) .negInf .posInf (-1) cert &&
    !Replay.check orderSign 7 p (x - 1) (.finite 0) .posInf (-1) cert

/- Positive independent denominator clearing preserves complete runtime
results, including the `none` cases and zero query polynomials. -/
#guard (#[0, C 5, Hex.QueryTests.p, -Hex.QueryTests.p,
    natPow Hex.QueryTests.x 2, scale 4 Hex.QueryTests.x] : Array ZPoly).all fun pz =>
  (#[0, 1, C (-1), Hex.QueryTests.x, Hex.QueryTests.x - 1,
    natPow Hex.QueryTests.x 8] : Array ZPoly).all fun fz =>
    let pr := scale (1 / 6 : Rat) (ZPoly.toRatPoly pz)
    let fr := scale (1 / 10 : Rat) (ZPoly.toRatPoly fz)
    let cp := ZPoly.clearDenominators pr
    let cf := ZPoly.clearDenominators fr
    0 < cp.1 && 0 < cf.1 &&
      query orderSign pr fr (.finite (-2)) (.finite 2) ==
        ZPoly.tarskiQuery cp.2 cf.2 Hex.QueryTests.interval &&
      query orderSign pr fr (.finite (-2)) (.finite 2) ==
        ZPoly.tarskiQuery pz fz Hex.QueryTests.interval

/- Negative clearing of the query changes its sign and is not an adapter. -/
#guard query orderSign (scale (1 / 6 : Rat) p) (C (-1 / 10)) .negInf .posInf == some (-2)

/- The same frontend accepts noncanonical arithmetic without a field instance. -/
#guard query Hex.QueryTests.Noncanonical.sign Hex.QueryTests.Noncanonical.head 1
  .negInf .posInf == some 2

/- Squarefreeness evidence is checked independently of the query chain. -/
#guard !Replay.check orderSign 7 p 1 (.finite (-2)) (.finite 2) 2
  { literal with squarefree := { literalChain with terminal := some (1, 1) } }

/- A constant tail alone cannot certify a repeated-root head. -/
#guard !Replay.check orderSign 7 (natPow (x - 1) 2) 1 (.finite (-2)) (.finite 2) 2
  { literal with
    head := natPow (x - 1) 2
    squarefree := { literalChain with chain := #[natPow (x - 1) 2, x - 1, 1] }
    remainders := { literalChain with chain := #[natPow (x - 1) 2, x - 1, 1] } }

/- Positive scales do not excuse a false initial reduction identity. -/
#guard !Replay.check orderSign 7 p 1 (.finite (-2)) (.finite 2) 2
  { literal with remainders := { literalChain with initial := ⟨1, 1, 2⟩ } }

theorem literal_checks : Replay.check orderSign 7 p 1 (.finite (-2)) (.finite 2) 2 literal = true := by
  simp only [Replay.check, QueryReplay.check, QueryChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

theorem stale_rejected : Replay.check orderSign 8 p 1 (.finite (-2)) (.finite 2) 2 literal = false := by
  decide +kernel

/-- info: 'Hex.Sturm.Conformance.literal_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_checks
/-- info: 'Hex.Sturm.Conformance.stale_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stale_rejected

end Hex.Sturm.Conformance
