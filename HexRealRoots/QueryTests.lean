/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Query
public import HexPoly.InterpretTests
public meta import HexPoly.InterpretTests
public meta import HexRealRoots.Query
public meta import HexRealRoots.QueryChain
public meta import HexRealRoots.Basic
public meta import HexPoly.Dense
public meta import HexPoly.Operations

public section

namespace Hex.QueryTests

open DensePoly
open scoped Hex

@[expose] def p : ZPoly := ofCoeffs #[-1, 0, 1]
@[expose] def x : ZPoly := ofCoeffs #[0, 1]
@[expose] def interval : DyadicInterval := ⟨Dyadic.ofInt (-2), Dyadic.ofInt 2, by decide +kernel⟩

#guard ZPoly.tarskiQuery p 1 interval == some 2
#guard ZPoly.tarskiQuery p (C (-1)) interval == some (-2)
#guard ZPoly.tarskiQuery p x interval == some 0
#guard ZPoly.tarskiQuery p (x - 1) interval == some (-1)
#guard ZPoly.tarskiQuery p p interval == some 0
#guard ZPoly.tarskiQuery p (natPow x 4) interval == some 2
#guard ZPoly.tarskiQuery p 0 interval == some 0
#guard ZPoly.tarskiQuery (C 5) (natPow x 4) interval == some 0
#guard ZPoly.tarskiQuery (scale 4 x) 1 interval == some 1
#guard ZPoly.tarskiQuery (-p) 1 interval == some 2
#guard ZPoly.tarskiQuery 0 0 interval == none
#guard ZPoly.tarskiQuery (natPow (x - 1) 2) 0 interval == none
#guard ZPoly.tarskiQuery p 0 ⟨Dyadic.ofInt (-1), Dyadic.ofInt 2, by decide +kernel⟩ == none

#guard match TarskiReplay.certify p (x - 1) interval with
  | none => false
  | some cert => cert.remainders.chain.size == 2 &&
    (cert.remainders.chain.getD 1 0).natDegree == 1 && TarskiReplay.check p (x - 1) interval (-1) cert

#guard match TarskiReplay.certify p p interval with
  | none => false
  | some cert => cert.remainders.chain.size == 1 && cert.remainders.terminal.isNone &&
    TarskiReplay.check p p interval 0 cert

#guard match TarskiReplay.certify p 1 interval with
  | none => false
  | some cert =>
    TarskiReplay.check p 1 interval 2 cert &&
    !TarskiReplay.check p 0 interval 2 cert &&
    !TarskiReplay.check p 1 interval 1 cert &&
    !TarskiReplay.check p 1 interval 2 { cert with lowerSigns := #[1, 1, 1] } &&
    !TarskiReplay.check p 1 interval 2
      { cert with remainders := { cert.remainders with terminal := none } } &&
    !TarskiReplay.check p 1 interval 2
      { cert with remainders := { cert.remainders with
        initial := { cert.remainders.initial with leftScale := -1 } } }

#guard match QueryReplay.certify Int.sign ZPoly.queryAdapter ZPoly.queryNormalize (7 : Nat)
    p 1 (.finite interval.lower) (.finite interval.upper) with
  | none => false
  | some cert => QueryReplay.check Int.sign ZPoly.queryAdapter 7 p 1
      (.finite interval.lower) (.finite interval.upper) 2 cert &&
    !QueryReplay.check Int.sign ZPoly.queryAdapter 8 p 1
      (.finite interval.lower) (.finite interval.upper) 2 cert

#guard QueryReplay.query Int.sign ZPoly.queryAdapter ZPoly.queryNormalize p 1 .negInf .posInf == some 2
#guard QueryReplay.query Int.sign ZPoly.queryAdapter ZPoly.queryNormalize p 0 .posInf .posInf == none
#guard QueryReplay.query Int.sign ZPoly.queryAdapter ZPoly.queryNormalize p 0 .posInf .negInf == none
#guard QueryReplay.query Int.sign ZPoly.queryAdapter ZPoly.queryNormalize p 0
  (.finite interval.upper) (.finite interval.lower) == none

/-- Literal certificate: replay does not regenerate a remainder chain. -/
@[expose] def literalChain : QueryChain Int where
  chain := #[p, x, 1]
  degrees := #[2, 1, 0]
  initial := ⟨1, 0, 2⟩
  steps := #[⟨1, x, 1⟩]
  terminal := some (1, x)

@[expose] def literal : TarskiReplay where
  context := ()
  head := p
  queryPoly := 1
  lower := .finite interval.lower
  upper := .finite interval.upper
  squarefree := literalChain
  remainders := literalChain
  lowerSigns := #[1, -1, 1]
  upperSigns := #[1, 1, 1]
  lowerVariations := 2
  upperVariations := 0
  value := 2

#guard TarskiReplay.check p 1 interval 2 literal



theorem literal_checks : TarskiReplay.check p 1 interval 2 literal = true := by
  simp only [TarskiReplay.check, QueryReplay.check, QueryChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

#guard !TarskiReplay.check p 1 interval 2
  { literal with remainders := { literalChain with degrees := #[2, 1, 1] } }
#guard !TarskiReplay.check p 1 interval 2
  { literal with remainders := { literalChain with steps := #[] } }
#guard !TarskiReplay.check p 1 interval 2
  { literal with remainders := { literalChain with steps := #[⟨1, x, 1⟩, ⟨1, x, 1⟩] } }
#guard !TarskiReplay.check p 1 interval 2
  { literal with remainders := { literalChain with chain := #[p, x, 1, 1] } }
#guard !TarskiReplay.check p 1 interval 2
  { literal with remainders := { literalChain with terminal := some (0, 0) } }

namespace Noncanonical
open HexPoly.InterpretTests

@[expose] def sign (a : Rep) : Int := (value a).num.sign
@[expose] def adapter : EndpointAdapter Rep Rep where
  compare a b := sign (a - b)
  evalSign p a := sign (p.eval a)

@[expose] def head : Poly := ofCoeffs #[-1, 0, root]
@[expose] def count : Option Int := QueryReplay.query sign adapter QueryChain.normalizeId head 1
  (.finite (pack (-2) 0)) (.finite (pack 2 0))
#guard count == some 2
#guard QueryReplay.query sign adapter QueryChain.normalizeId head (C root) .negInf .posInf == some 2
#guard QueryReplay.query sign adapter QueryChain.normalizeId head 0 .negInf .posInf == some 0

-- The two literal query polynomials are semantically equal but replay bindings
-- still reject substitution of the unbound representative.
#guard match QueryReplay.certify sign adapter QueryChain.normalizeId () head (C root)
    .negInf .posInf with
  | none => false
  | some cert => QueryReplay.check sign adapter () head (C root) .negInf .posInf 2 cert &&
    !QueryReplay.check sign adapter () head 1 .negInf .posInf 2 cert

end Noncanonical

/-- info: 'Hex.QueryTests.literal_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_checks

end Hex.QueryTests
