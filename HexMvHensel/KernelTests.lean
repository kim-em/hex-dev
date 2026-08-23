/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvHensel.Shift
public import HexMvHensel.Modulus

public section

/-!
Small kernel-reduction checks for the coordinate and modulus layer.
-/

namespace Hex.MvHensel.KernelTests

open Hex
open Hex.MvPoly
open scoped Hex

abbrev P2 := MvPoly 2 Int Mono.lex

@[expose] def x : P2 := X 0
@[expose] def y : P2 := X 1

@[expose] def target : P2 := x * x + y * x + C 2 * y + C 1

@[expose] def point3 : Fin 1 → Int := fun _ => 3

example : shift 0 point3 target =
    ofTerms
      [(#v[2, 0], 1), (#v[1, 1], 1), (#v[1, 0], 3),
       (#v[0, 1], 2), (Mono.zero, 7)] := by
  decide +kernel

example : unshift 0 point3 (shift 0 point3 target) = target := by
  decide +kernel

example : lcIn 0 Mono.lex target = (1 : MvPoly 1 Int Mono.lex) := by
  decide +kernel

@[expose] def outsideBox : P2 :=
  ofTerms [(#v[2, 0], 1), (#v[1, 1], 2), (#v[0, 2], 3), (Mono.zero, 4)]

example : truncate 0 (fun _ => 1) outsideBox =
    ofTerms [(#v[2, 0], 1), (#v[1, 1], 2), (Mono.zero, 4)] := by
  decide +kernel

example : reduceMod 5
    (ofTerms [(#v[1, 0], 7), (#v[0, 1], 3), (Mono.zero, -4)] : P2) =
    ofTerms [(#v[1, 0], 2), (#v[0, 1], -2), (Mono.zero, 1)] := by
  decide +kernel

abbrev P1 := MvPoly 1 Int Mono.lex

@[expose] def noPoint : Fin 0 → Int := fun j => nomatch j

example : shift 0 noPoint ((X 0 : P1) * X 0 + C 2) =
    (X 0 : P1) * X 0 + C 2 := by
  decide +kernel

end Hex.MvHensel.KernelTests
