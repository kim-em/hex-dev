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

theorem splitFirst_roundtrip :
    ofUnivariate (cmp := Mono.grevlex) 0 Mono.lex
      (toUnivariate 0 Mono.lex q) = q := by
  decide +kernel

theorem splitLast_roundtrip :
    ofUnivariate (cmp := Mono.grevlex) 1 Mono.lex
      (toUnivariate 1 Mono.lex q) = q := by
  decide +kernel

@[expose] def gapCoeffs : DensePoly (MvPoly 1 Rat Mono.lex) :=
  DensePoly.ofList [C 2 + X 0, 0, C 3]

theorem gapCoeffs_roundtrip :
    toUnivariate 1 Mono.lex
        (ofUnivariate (cmp := Mono.grevlex) 1 Mono.lex gapCoeffs) =
      gapCoeffs := by
  decide +kernel

abbrev P3 := MvPoly 3 Int Mono.lex

@[expose] def middleSplit : P3 :=
  ofTerms [(#v[2, 3, 4], 5), (#v[0, 1, 2], -7), (Mono.zero, 11)]

theorem middleSplit_roundtrip :
    ofUnivariate (cmp := Mono.lex) 1 Mono.grevlex
      (toUnivariate 1 Mono.grevlex middleSplit) = middleSplit := by
  decide +kernel

theorem zero_roundtrip :
    ofUnivariate (cmp := Mono.grevlex) 1 Mono.lex
      (toUnivariate 1 Mono.lex (0 : QP)) = 0 := by
  decide +kernel

abbrev P0 := MvPoly 0 Int Mono.lex

example : (C 7 : P0) + C (-7) = 0 := by
  decide +kernel

example : evalHorner (fun i => nomatch i) (C 7 : P0) = 7 := by
  decide +kernel

abbrev P1 := MvPoly 1 Int Mono.lex

theorem oneVar_roundtrip :
    ofUnivariate (cmp := Mono.lex) 0 Mono.lex
      (toUnivariate 0 Mono.lex ((X 0 : P1) * X 0 + C 7)) =
        (X 0 : P1) * X 0 + C 7 := by
  decide +kernel

example : (X 0 : P1) * X 0 = monomial
    (Mono.succAt 0 (Mono.unit 0)) 1 := by
  decide +kernel

/-! # Axiom hygiene -/

/-- info: 'Hex.MvPoly.KernelTests.splitFirst_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitFirst_roundtrip

/-- info: 'Hex.MvPoly.KernelTests.splitLast_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitLast_roundtrip

/-- info: 'Hex.MvPoly.KernelTests.gapCoeffs_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gapCoeffs_roundtrip

/-- info: 'Hex.MvPoly.KernelTests.middleSplit_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms middleSplit_roundtrip

/-- info: 'Hex.MvPoly.KernelTests.zero_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_roundtrip

/-- info: 'Hex.MvPoly.KernelTests.oneVar_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oneVar_roundtrip

end Hex.MvPoly.KernelTests
