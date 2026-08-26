/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvHensel

/-!
Executable conformance checks for checked multivariate Hensel lifting.

Oracle: SymPy `dup_zz_diophantine`, `dmp_zz_diophantine`, and
`dmp_zz_wang_hensel_lifting`
Mode: always
Covered operations:
- `shift`, `unshift`, `imageAt`, `lcIn`, `truncate`, and `reduceMod`
- `witnessOf?`, `solveUni`, and recursive `diophantine`
- `seed`, `setLc`, `valid`, `failure?`, and `coeffBound`
- checked `lift`, `liftWith`, and certificate `check`
Covered edge cases:
- one through five factors and one through five variables
- nonconstant and shared leading coefficients, including coefficients larger
  than the working modulus
- linear main variable, coarse and degenerate splittings, and arity one
- non-squarefree images, a bad resultant prime, and an unlucky split point
- insufficient reconstruction precision and a far-from-origin evaluation point
- nested diophantine recursion and its load-bearing degree rejection
-/

namespace Hex.MvHensel.Conformance

open Hex
open Hex.MvPoly
open scoped Hex

private def prime2 : ZMod64.Prime where
  m := 2
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

private def prime3 : ZMod64.Prime where
  m := 3
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

private def prime5 : ZMod64.Prime where
  m := 5
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

private def prime101 : ZMod64.Prime where
  m := 101
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

private def inputOf? {n : Nat} (point : Fin n → Int)
    (prime : ZMod64.Prime) (exponent : Nat)
    (factors : List (MvPoly (n + 1) Int Mono.lex)) :
    Option (Input n Mono.lex Mono.lex) := do
  let setup : Setup n :=
    { main := 0, point := point, prime := prime, exponent := exponent }
  let images := factors.map (imageAt setup.main Mono.lex point)
  let leading := factors.map (lcIn setup.main Mono.lex)
  let witness ← witnessOf? setup images
  some
    { setup := setup
      target := mvProduct factors
      images := images
      leading := leading
      witness := witness }

private def liftsTo {n : Nat} (inp : Input n Mono.lex Mono.lex)
    (expected : List (MvPoly (n + 1) Int Mono.lex)) : Bool :=
  match lift inp with
  | .ok cert => cert.factors == expected && check inp cert
  | .error _ => false

private def liftsWithTo {n : Nat} (doublings : Nat)
    (inp : Input n Mono.lex Mono.lex)
    (expected : List (MvPoly (n + 1) Int Mono.lex)) : Bool :=
  match liftWith { doublings := doublings } inp with
  | .ok cert => cert.factors == expected && check inp cert
  | .error _ => false

/-! Coordinate, modulus, seed, and univariate contracts. -/

#guard
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let point : Fin 1 → Int := fun _ => 3
  let target := x ^ 2 + y * x + 2 * y + 1
  unshift 0 point (shift 0 point target) == target &&
    imageAt 0 Mono.lex point target == DensePoly.ofCoeffs #[7, 3, 1] &&
    lcIn 0 Mono.lex target == 1

#guard
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let degrees : Fin 1 → Nat := fun _ => 1
  truncate 0 degrees (x ^ 2 + 2 * x * y + 3 * y ^ 2 + 4) ==
    x ^ 2 + 2 * x * y + 4

#guard
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  reduceMod 5 (7 * x + 3 * y - 4) == 2 * x - 2 * y + 1

private def ux : ZPoly := DensePoly.ofCoeffs #[0, 1]
private def uxPlusOne : ZPoly := DensePoly.ofCoeffs #[1, 1]
private def images : List ZPoly := [ux, uxPlusOne]
private def witness : List ZPoly := [1, -1]

#guard solveUni 5 images witness 1 == [1, -1]
#guard solveUni 5 images witness ux == [0, 1]
#guard solveUni 5 images witness 0 == [0, 0]

#guard
  let noPoint : Fin 0 → Int := fun j => nomatch j
  let setup : Setup 0 :=
    { main := 0, point := noPoint, prime := prime5, exponent := 1 }
  match witnessOf? setup images with
  | some derived =>
      coeffsDivisible setup.modulus
        (zSub (uniCombination derived (complements images)) 1)
  | none => false

#guard
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let ly : MvPoly 1 Int Mono.lex := X 0
  seed (cmp := Mono.lex) (0 : Fin 2) Mono.lex (ly + 1)
      (DensePoly.ofCoeffs #[2, 3]) == 2 + (y + 1) * x &&
    setLc (cmp := Mono.lex) (0 : Fin 2) Mono.lex (ly + 1)
      (x ^ 2 + y * x + 1) == (y + 1) * x ^ 2 + y * x + 1

/-! Factor-count coverage at two variables. -/

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [x + y + 1, x + 2]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [x + y + 1, x + 2, x + 3]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [x + y + 1, x + 2, x + 3, x + 4]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [x + y + 1, x + 2, x + 3, x + 4, x + 5]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

/-! Variable-count coverage through five variables. -/

#guard
  let point : Fin 2 → Int := fun _ => 0
  let x : MvPoly 3 Int Mono.lex := X 0
  let factors := [x + X 1 + X 2 + 1, x + 2]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 3 → Int := fun _ => 0
  let x : MvPoly 4 Int Mono.lex := X 0
  let factors := [x + X 1 + X 2 + X 3 + 1, x + 2]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 4 → Int := fun _ => 0
  let x : MvPoly 5 Int Mono.lex := X 0
  let factors := [x + X 1 + X 2 + X 3 + X 4 + 1, x + 2]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

/-! Leading coefficients, grouping, and boundary arities. -/

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let shared := y + 1
  let factors := [shared * x + 1, shared * x + 2]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [(y + 6) * x + 1, x + 2]
  match inputOf? point prime5 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [(y + 1) * x + y + 2]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let a := x + y + 1
  let b := x + 2
  let c := x + 3
  let factors := [a * b, c]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

#guard
  let point : Fin 0 → Int := fun j => nomatch j
  let x : MvPoly 1 Int Mono.lex := X 0
  let factors := [x, x + 1]
  match inputOf? point prime101 1 factors with
  | some inp => liftsTo inp factors
  | none => false

/-! Validation and reconstruction traps. -/

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let setup : Setup 1 :=
    { main := 0, point := point, prime := prime5, exponent := 1 }
  let inp : Input 1 Mono.lex Mono.lex :=
    { setup := setup
      target := (x + y) * (x - y)
      images := [DensePoly.ofCoeffs #[0, 1], DensePoly.ofCoeffs #[0, 1]]
      leading := [1, 1]
      witness := [0, 0] }
  failure? inp == some .notCoprime

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [x + y - 1, x + y + 1]
  let badSetup : Setup 1 :=
    { main := 0, point := point, prime := prime2, exponent := 1 }
  let bad : Input 1 Mono.lex Mono.lex :=
    { setup := badSetup
      target := mvProduct factors
      images := factors.map (imageAt badSetup.main Mono.lex point)
      leading := factors.map (lcIn badSetup.main Mono.lex)
      witness := [0, 0] }
  failure? bad == some .notCoprime &&
    match inputOf? point prime3 1 factors with
    | some good => liftsTo good factors
    | none => false

#guard
  let point : Fin 1 → Int := fun _ => -1
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let inp : Input 1 Mono.lex Mono.lex :=
    { setup := { main := 0, point := point, prime := prime5, exponent := 1 }
      target := x ^ 2 + y
      images := [DensePoly.ofCoeffs #[-1, 1], DensePoly.ofCoeffs #[1, 1]]
      leading := [1, 1]
      witness := [DensePoly.C (-2), DensePoly.C 2] }
  match lift inp with
  | .error (.reconstruct 5) => true
  | _ => false

#guard
  let point : Fin 1 → Int := fun _ => 0
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [x + 3 * y, x + 1]
  match inputOf? point prime5 1 factors with
  | some inp =>
      (match lift inp with
       | .error (.reconstruct 5) => true
       | _ => false) && liftsWithTo 1 inp factors
  | none => false

#guard
  let point : Fin 1 → Int := fun _ => 10
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let factors := [x + y ^ 2, x + 1]
  match inputOf? point prime101 1 factors with
  | some inp => coeffBound inp == 5075 && liftsTo inp factors
  | none => false

/-! Direct recursive diophantine contracts and failures. -/

#guard
  let x : MvPoly 1 Int Mono.lex := X 0
  let degrees : Fin 0 → Nat := fun j => nomatch j
  diophantine 5 (0 : Fin 1) Mono.lex degrees
    [x + 1, x] images witness 1 == some [1, -1]

#guard
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let degrees : Fin 1 → Nat := fun _ => 1
  diophantine 5 (0 : Fin 2) Mono.lex degrees
    [x + 1, x] images witness (1 + y * x) == some [1, -1 + y]

#guard
  let x : MvPoly 3 Int Mono.lex := X 0
  let y : MvPoly 3 Int Mono.lex := X 1
  let z : MvPoly 3 Int Mono.lex := X 2
  let degrees : Fin 2 → Nat := fun _ => 1
  diophantine 5 (0 : Fin 3) Mono.lex degrees
    [x + 1, x] images witness
      (1 + y * x + z * (x + 1) + y * z) ==
    some [1 + z + y * z, -1 + y - y * z]

#guard
  let x : MvPoly 2 Int Mono.lex := X 0
  let y : MvPoly 2 Int Mono.lex := X 1
  let degrees : Fin 1 → Nat := fun _ => 1
  (diophantine 5 (0 : Fin 2) Mono.lex degrees
    [x + 1 + y * x ^ 3, x] images witness 1).isNone

end Hex.MvHensel.Conformance
