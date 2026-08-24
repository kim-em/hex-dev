/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvFactor.Leading
public import HexMvFactor.Leading

public section

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

private def y : MvPoly 1 Int Mono.lex := X 0
private def atFive : Fin 1 → Int := fun _ => 5
private def h₁ : ZPoly := DensePoly.ofList [1, 10]
private def h₂ : ZPoly := DensePoly.ofList [5, 3]

/- The integer content is forced across both leading coefficients:
   `(2y, 3)`, not `(6y, 1)`. -/
private def splitContent : Decomp 1 Mono.lex :=
  { content := 6
    factors := [⟨y, 1⟩] }

#guard
  match distribute? 0 Mono.lex atFive splitContent [h₁, h₂] 1 with
  | some (leading, images) =>
      leading == [C 2 * y, C 3] && images == [h₁, h₂]
  | none => false

/- The separated residual of `Ω(5) = 6` against scalar `2` is `3`, but
   multiplicity counting must still divide by the full value `6`.  Only one
   full division is available, so an asserted multiplicity two is rejected. -/
private def sharedScalar : Decomp 1 Mono.lex :=
  { content := 2
    factors := [⟨y + 1, 2⟩] }

private def sharedImage : ZPoly := DensePoly.ofList [1, 9]

#guard nonDivisors 2 [6] == some [3]
#guard distribute? 0 Mono.lex atFive sharedScalar [sharedImage] 8 |>.isNone

/- A value without a factor distinct from all earlier values is rejected by
   the non-divisor condition. -/
#guard nonDivisors 6 [12] |>.isNone

end Hex.MvFactor
