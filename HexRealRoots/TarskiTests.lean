/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Tarski
public import HexPoly.InterpretTests
public meta import HexPoly.InterpretTests
public meta import HexRealRoots.Tarski
public meta import HexRealRoots.SignedRemainderChain
public meta import HexRealRoots.Basic
public meta import HexPoly.Dense
public meta import HexPoly.Operations

public section

namespace Hex.TarskiTests

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

#guard match IntTarskiCertificate.certify p (x - 1) interval with
  | none => false
  | some cert => cert.remainders.chain.size == 2 &&
    (cert.remainders.chain.getD 1 0).natDegree == 1 && IntTarskiCertificate.check p (x - 1) interval (-1) cert

#guard match IntTarskiCertificate.certify p p interval with
  | none => false
  | some cert => cert.remainders.chain.size == 1 && cert.remainders.terminal.isNone &&
    IntTarskiCertificate.check p p interval 0 cert

#guard match IntTarskiCertificate.certify p 1 interval with
  | none => false
  | some cert =>
    IntTarskiCertificate.check p 1 interval 2 cert &&
    !IntTarskiCertificate.check p 0 interval 2 cert &&
    !IntTarskiCertificate.check p 1 interval 1 cert &&
    !IntTarskiCertificate.check p 1 interval 2 { cert with lowerSigns := #[1, 1, 1] } &&
    !IntTarskiCertificate.check p 1 interval 2
      { cert with remainders := { cert.remainders with terminal := none } } &&
    !IntTarskiCertificate.check p 1 interval 2
      { cert with remainders := { cert.remainders with
        initial := { cert.remainders.initial with leftScale := -1 } } }

#guard match TarskiCertificate.certify Int.sign EndpointSigns.intDyadic ZPoly.normalizeContent (7 : Nat)
    p 1 (.finite interval.lower) (.finite interval.upper) with
  | none => false
  | some cert => TarskiCertificate.check Int.sign EndpointSigns.intDyadic 7 p 1
      (.finite interval.lower) (.finite interval.upper) 2 cert &&
    !TarskiCertificate.check Int.sign EndpointSigns.intDyadic 8 p 1
      (.finite interval.lower) (.finite interval.upper) 2 cert

#guard TarskiCertificate.query Int.sign EndpointSigns.intDyadic ZPoly.normalizeContent p 1 .negInf .posInf == some 2
#guard TarskiCertificate.query Int.sign EndpointSigns.intDyadic ZPoly.normalizeContent p 0 .posInf .posInf == none
#guard TarskiCertificate.query Int.sign EndpointSigns.intDyadic ZPoly.normalizeContent p 0 .posInf .negInf == none
#guard TarskiCertificate.query Int.sign EndpointSigns.intDyadic ZPoly.normalizeContent p 0
  (.finite interval.upper) (.finite interval.lower) == none

/-- Literal certificate: replay does not regenerate a remainder chain. -/
@[expose] def literalChain : SignedRemainderChain Int where
  chain := #[p, x, 1]
  degrees := #[2, 1, 0]
  initial := ⟨1, 0, 2⟩
  steps := #[⟨1, x, 1⟩]
  terminal := some (1, x)

@[expose] def literal : IntTarskiCertificate where
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

#guard IntTarskiCertificate.check p 1 interval 2 literal



theorem literal_checks : IntTarskiCertificate.check p 1 interval 2 literal = true := by
  simp only [IntTarskiCertificate.check, TarskiCertificate.check, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

#guard !IntTarskiCertificate.check p 1 interval 2
  { literal with remainders := { literalChain with degrees := #[2, 1, 1] } }
#guard !IntTarskiCertificate.check p 1 interval 2
  { literal with remainders := { literalChain with steps := #[] } }
#guard !IntTarskiCertificate.check p 1 interval 2
  { literal with remainders := { literalChain with steps := #[⟨1, x, 1⟩, ⟨1, x, 1⟩] } }
#guard !IntTarskiCertificate.check p 1 interval 2
  { literal with remainders := { literalChain with chain := #[p, x, 1, 1] } }
#guard !IntTarskiCertificate.check p 1 interval 2
  { literal with remainders := { literalChain with terminal := some (0, 0) } }

namespace Noncanonical
open HexPoly.InterpretTests

@[expose] def sign (a : Rep) : Int := (value a).num.sign
@[expose] def endpointSigns : EndpointSigns Rep Rep where
  compare a b := sign (a - b)
  evalSign p a := sign (p.eval a)

@[expose] def head : Poly := ofCoeffs #[-1, 0, root]
@[expose] def count : Option Int := TarskiCertificate.query sign endpointSigns SignedRemainderChain.normalizeId head 1
  (.finite (pack (-2) 0)) (.finite (pack 2 0))
#guard count == some 2
#guard TarskiCertificate.query sign endpointSigns SignedRemainderChain.normalizeId head (C root) .negInf .posInf == some 2
#guard TarskiCertificate.query sign endpointSigns SignedRemainderChain.normalizeId head 0 .negInf .posInf == some 0

-- The two literal query polynomials are semantically equal but replay bindings
-- still reject substitution of the unbound representative.
#guard match TarskiCertificate.certify sign endpointSigns SignedRemainderChain.normalizeId () head (C root)
    .negInf .posInf with
  | none => false
  | some cert => TarskiCertificate.check sign endpointSigns () head (C root) .negInf .posInf 2 cert &&
    !TarskiCertificate.check sign endpointSigns () head 1 .negInf .posInf 2 cert

end Noncanonical

/-- info: 'Hex.TarskiTests.literal_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_checks

end Hex.TarskiTests
