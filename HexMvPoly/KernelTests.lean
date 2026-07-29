/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly

public section

/-!
Downstream module-boundary checks for the kernel-reduction closure of
`Hex.MvPoly`.
-/

namespace Hex.MvPoly.KernelTests

open Hex
open scoped Hex

abbrev P := MvPoly 2 Int Mono.lex

@[expose] def x : P := X 0
@[expose] def y : P := X 1
@[expose] def p : P := C 1 + x + y

example : p + -p = 0 := by
  decide +kernel

example : (p == p) = true := by
  decide +kernel

example : coeff (Mono.unit 0) p = 1 := by
  decide +kernel

example :
    p * p =
      ofTerms
        [(Mono.zero, 1),
         (Mono.unit 0, 2),
         (Mono.unit 1, 2),
         (Mono.mul (Mono.unit 0) (Mono.unit 0), 1),
         (Mono.mul (Mono.unit 0) (Mono.unit 1), 2),
         (Mono.mul (Mono.unit 1) (Mono.unit 1), 1)] := by
  decide +kernel

example : p ^ 3 = p * p * p := by
  decide +kernel

example : Mono.powBySq (3 : Int) 13 = 1594323 := by
  decide +kernel

example :
    Mono.dvd (Mono.unit 0 : Mono 2)
      (Mono.succAt 0 (Mono.unit 0 : Mono 2)) = true := by
  decide +kernel

example :
    Mono.div (Mono.unit 0 : Mono 2)
        (Mono.succAt 0 (Mono.unit 0 : Mono 2)) =
      some (Mono.unit 0 : Mono 2) := by
  decide +kernel

example :
    Mono.lcm (Mono.unit 0 : Mono 2) (Mono.unit 1 : Mono 2) =
      Mono.mul (Mono.unit 0 : Mono 2) (Mono.unit 1 : Mono 2) := by
  decide +kernel

example :
    Mono.gcd (Mono.unit 0 : Mono 2) (Mono.unit 1 : Mono 2) = Mono.zero := by
  decide +kernel

abbrev GP := MvPoly 2 Int Mono.grlex

@[expose] def gx : GP := X 0
@[expose] def gy : GP := X 1

example : gx * gy + gy * gx = ofTerms
    [(Mono.mul (Mono.unit 0) (Mono.unit 1), 2)] := by
  decide +kernel

abbrev QP := MvPoly 2 Rat Mono.grevlex

@[expose] def qx : QP := X 0
@[expose] def qy : QP := X 1
@[expose] def q : QP := C (1 / 2) + qx + qy

example : q * (qx - qy) + q * (qy - qx) = 0 := by
  decide +kernel

example : eval (fun i => if i = 0 then 2 else 3) q = 11 / 2 := by
  decide +kernel

@[expose] def sparse : P :=
  ofTerms
    [(#v[4, 0], 2), (#v[1, 2], 3), (#v[0, 3], -1), (Mono.zero, 5)]

example :
    evalHorner (fun i => if i = 0 then 2 else 3) sparse = 64 := by
  decide +kernel

example :
    evalHorner (fun i => if i = 0 then 2 else 3) sparse =
      eval (fun i => if i = 0 then 2 else 3) sparse := by
  decide +kernel

@[expose] def outerGap : P :=
  ofTerms [(#v[4, 0], 2), (#v[2, 1], 3)]

example :
    evalHorner (fun i => if i = 0 then 2 else 3) outerGap = 68 := by
  decide +kernel

example :
    ofUnivariate (cmp := Mono.grevlex) 0 Mono.lex
      (toUnivariate 0 Mono.lex q) = q := by
  decide +kernel

abbrev P0 := MvPoly 0 Int Mono.lex

example : (C 7 : P0) + C (-7) = 0 := by
  decide +kernel

example : evalHorner (fun i => nomatch i) (C 7 : P0) = 7 := by
  decide +kernel

abbrev P1 := MvPoly 1 Int Mono.lex

example : (X 0 : P1) * X 0 = monomial
    (Mono.succAt 0 (Mono.unit 0)) 1 := by
  decide +kernel

end Hex.MvPoly.KernelTests
