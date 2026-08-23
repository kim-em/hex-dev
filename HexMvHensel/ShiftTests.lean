/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexMvHensel.Shift
public meta import HexMvHensel.Shift
import all HexMvPoly

section

namespace Hex.MvHensel.ShiftTests

open Hex
open Hex.MvPoly

abbrev P0 := MvPoly 0 Int Mono.lex
abbrev P2 := MvPoly 2 Int Mono.lex
abbrev P3 := MvPoly 3 Int Mono.lex

/-- Direct substitution retained only as an executable reference oracle for
the production synthetic-division shift. -/
def directShiftAll {n : Nat} (a : Fin n → Int)
    (p : MvPoly n Int Mono.lex) : MvPoly n Int Mono.lex :=
  MvPoly.subst (fun j => X j + C (a j)) p

def directShift {n : Nat} (i : Fin (n + 1)) (a : Fin n → Int)
    (p : MvPoly (n + 1) Int Mono.lex) : MvPoly (n + 1) Int Mono.lex :=
  MvPoly.subst (shiftVar i a) p

def directImage {n : Nat} (i : Fin (n + 1)) (a : Fin n → Int)
    (p : MvPoly (n + 1) Int Mono.lex) : DensePoly Int :=
  let view := MvPoly.toUnivariate i Mono.lex p
  DensePoly.ofCoeffs (view.toArray.map fun coefficient => MvPoly.eval a coefficient)

def point2 : Fin 2 → Int
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => -1

def pointAround1 : Fin 2 → Int
  | ⟨0, _⟩ => -2
  | ⟨1, _⟩ => 3

/- Arity zero and zero-degree inputs exercise the empty synthetic loop. -/
#guard shiftAll (fun j : Fin 0 => nomatch j) (C 7 : P0) == C 7

/- Sparse gaps, mixed terms, negative points, and cancellation agree with the
direct substitution semantics. -/
#guard
  let x : P2 := X 0
  let y : P2 := X 1
  let p := 3 * x ^ 4 * y ^ 2 - 2 * x ^ 2 + 5 * y ^ 3 + x * y - 7
  shiftAll point2 p == directShiftAll point2 p

/- A named main variable is fixed while both surrounding variables shift. -/
#guard
  let x : P3 := X 0
  let y : P3 := X 1
  let z : P3 := X 2
  let p := x ^ 3 * y ^ 2 + 2 * y * z ^ 2 - x * z + 4
  shift (1 : Fin 3) pointAround1 p ==
    directShift (1 : Fin 3) pointAround1 p

#guard
  let y : P3 := X 1
  shift (1 : Fin 3) pointAround1 y == y

#guard
  let x : P3 := X 0
  let y : P3 := X 1
  let z : P3 := X 2
  let p := x ^ 3 * y ^ 2 + 2 * y * z ^ 2 - x * z + 4
  unshift (1 : Fin 3) pointAround1 (shift (1 : Fin 3) pointAround1 p) == p

/- Horner evaluation of every main-variable slice agrees with the direct
sparse evaluator, including a non-leading main variable. -/
#guard
  let x : P3 := X 0
  let y : P3 := X 1
  let z : P3 := X 2
  let p := x ^ 4 * y ^ 3 + 2 * y ^ 2 * z ^ 5 - 3 * x * z + 9
  imageAt (1 : Fin 3) Mono.lex pointAround1 p ==
    directImage (1 : Fin 3) pointAround1 p

end Hex.MvHensel.ShiftTests
