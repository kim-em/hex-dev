/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSparsePoly
import HexModArith

/-!
Single source of committed inputs shared by HexSparsePoly's Lean
conformance checks and JSONL emit driver. `ZMod64` comes from
hex-mod-arith, which the conformance project pins even though the
library does not depend on it (see the SPEC's Conformance section).
-/

namespace Hex.SparsePolyFixtures

open Hex
open Hex.SparsePoly

abbrev PZ := SparsePoly Int
abbrev PQ := SparsePoly Rat

instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
instance boundsSix : ZMod64.Bounds 6 := ⟨by decide, by decide⟩
instance boundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

abbrev P5 := SparsePoly (ZMod64 5)
abbrev P6 := SparsePoly (ZMod64 6)
abbrev P7 := SparsePoly (ZMod64 7)

/-- Disjoint supports: no exponent shared with `qDisjoint`. -/
def pDisjoint : PZ := #sp[(0, 3), (5, -2), (9, 4)]

def qDisjoint : PZ := #sp[(2, 7), (11, -5)]

/-- Heavily overlapping supports against `qOverlap`, with cancellation
at the lowest and an interior exponent. -/
def pOverlap : PZ := #sp[(0, 1), (3, 4), (5, 2)]

def qOverlap : PZ := #sp[(0, -1), (3, -4), (7, 2)]

/-- Binomial at degree `10^3`. -/
def binom3 : PZ := #sp[(0, -1), (1000, 1)]

/-- Trinomial at degree `10^4`. -/
def tri4 : PZ := #sp[(0, -5), (17, 2), (10000, 1)]

/-- The SPEC's flagship input: `x^1000000 − 1`. Two terms against a
million dense coefficients; no dense route in the suite may touch it. -/
def binom6 : PZ := #sp[(0, -1), (1000000, 1)]

/-- Trinomial at degree `10^6`. -/
def tri6 : PZ := #sp[(0, 1), (500000, 1), (1000000, 1)]

/-- `Φ_3 = 1 + x + x²`, the dense seed of the `Φ_{3^k}` family. -/
def phi3 : PZ := #sp[(0, 1), (1, 1), (2, 1)]

/-- `Φ_5 = 1 + x + x² + x³ + x⁴`. -/
def phi5 : PZ := #sp[(0, 1), (1, 1), (2, 1), (3, 1), (4, 1)]

/-- Rational coefficients. -/
def pRat : PQ := #sp[(0, (1 : Rat) / 2), (4, -(3 : Rat) / 7)]

def qRat : PQ := #sp[(0, -(1 : Rat) / 2), (4, (2 : Rat) / 3), (6, 5)]

/-- `ZMod64 7` polynomial whose exponents include multiples of `7`. -/
def pMod7 : P7 :=
  #sp[(1, ZMod64.ofNat 7 3), (7, ZMod64.ofNat 7 1), (14, ZMod64.ofNat 7 6)]

/-- High-exponent `ZMod64 7` polynomial: the oracle can evaluate it and
a dense evaluation could not run. -/
def pMod7Big : P7 :=
  #sp[(0, ZMod64.ofNat 7 2), (1000003, ZMod64.ofNat 7 4)]

/-- Wire form of an `Int` polynomial: ascending
`(exponent, numerator, denominator)` triples. -/
def wireInt (s : PZ) : List (Nat × Int × Int) :=
  s.toTerms.map fun t => (t.1, t.2, 1)

/-- Wire form of a `Rat` polynomial. -/
def wireRat (s : PQ) : List (Nat × Int × Int) :=
  s.toTerms.map fun t => (t.1, t.2.num, (t.2.den : Int))

/-- Wire form of a `ZMod64 p` polynomial. -/
def wireMod {p : Nat} [ZMod64.Bounds p] (s : SparsePoly (ZMod64 p)) :
    List (Nat × Int × Int) :=
  s.toTerms.map fun t => (t.1, (ZMod64.toNat t.2 : Int), 1)

end Hex.SparsePolyFixtures
