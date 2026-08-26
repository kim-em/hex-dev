/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus

public section

open Hex

private def zp (cs : Array Int) : ZPoly := DensePoly.ofCoeffs cs

private def showF (name : String) (f : ZPoly) : IO Unit := do
  let φ : Factorization := Hex.factor f
  IO.println s!"--- {name}"
  IO.println s!"  scalar: {φ.scalar}"
  for (g, m) in φ.factors do
    IO.println s!"  factor^{m}: {g.toArray.toList}"

@[expose]
def main : IO Unit := do
  showF "x^5 - 1" (zp #[-1,0,0,0,0,1])
  showF "x^4 + 1" (zp #[1,0,0,0,1])
  showF "(x^2-2)(x^2-3)" (zp #[6,0,-5,0,1])
  showF "Phi_15" (zp #[1,-1,0,1,-1,1,0,-1,1])
  let prod5 := (zp #[-1,1]) * (zp #[-2,1]) * (zp #[-3,1]) * (zp #[-4,1]) * (zp #[-5,1])
  showF "(x-1)..(x-5)" prod5
