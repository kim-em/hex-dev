/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvPoly

/-!
Single source of committed inputs shared by HexMvPoly's Lean conformance
checks and JSONL emit driver.
-/

namespace Hex.MvPolyFixtures

open Hex
open Hex.MvPoly

abbrev P0 := MvPoly 0 Int Mono.grlex
abbrev P1 := MvPoly 1 Int Mono.lex
abbrev P2 := MvPoly 2 Int Mono.grlex
abbrev P3 := MvPoly 3 Int Mono.grlex

def duplicateTerms : List (Mono 3 × Int) := [
  (#v[2, 0, 1], 4),
  (#v[0, 1, 0], 7),
  (#v[2, 0, 1], -3),
  (#v[0, 1, 0], -7),
  (#v[1, 1, 0], 5)]

def duplicateInput : P3 :=
  ofTerms duplicateTerms

def addLeft : P3 :=
  ofTerms [(#v[2, 0, 0], 3), (#v[0, 1, 0], -4), (Mono.zero, 2)]

def addRight : P3 :=
  ofTerms [(#v[2, 0, 0], -3), (#v[0, 1, 0], 9), (Mono.zero, -2)]

def mulLeft : P3 :=
  ofTerms [(#v[1, 0, 0], 1), (Mono.zero, 1)]

def mulRight : P3 :=
  ofTerms [(#v[1, 0, 0], 1), (Mono.zero, -1)]

def renameInput : P2 :=
  ofTerms [(#v[1, 0], 3), (#v[0, 1], -3), (Mono.zero, 4)]

def substInput : P2 :=
  ofTerms [(#v[1, 0], 3), (#v[0, 1], -1), (#v[1, 1], 2)]

def partialInput : P2 :=
  ofTerms [
    (#v[1, 0], 1),
    (Mono.zero, -2),
    (#v[0, 1], 4),
    (#v[1, 1], -2)]

def viewInput : P3 :=
  ofTerms [
    (#v[3, 0, 1], 2),
    (#v[0, 2, 4], -5),
    (#v[1, 1, 0], 7),
    (#v[1, 0, 1], 11),
    (#v[0, 2, 0], -13),
    (Mono.zero, 3)]

def arityZero : P0 :=
  ofTerms [(Mono.zero, 4), (Mono.zero, -9), (Mono.zero, 6)]

def zero3 : P3 := 0

def constant3 : P3 := C (-7)

end Hex.MvPolyFixtures
