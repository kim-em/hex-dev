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

private def splitProduct (n : Nat) : ZPoly := Id.run do
  let mut acc : ZPoly := 1
  for i in [1:n+1] do
    acc := acc * (zp #[-(Int.ofNat i), 1])
  return acc

private instance b3  : ZMod64.Bounds 3  := ⟨by decide, by decide⟩
private instance b5  : ZMod64.Bounds 5  := ⟨by decide, by decide⟩
private instance b7  : ZMod64.Bounds 7  := ⟨by decide, by decide⟩
private instance b11 : ZMod64.Bounds 11 := ⟨by decide, by decide⟩
private instance b13 : ZMod64.Bounds 13 := ⟨by decide, by decide⟩
private instance b17 : ZMod64.Bounds 17 := ⟨by decide, by decide⟩
private instance b19 : ZMod64.Bounds 19 := ⟨by decide, by decide⟩
private instance b23 : ZMod64.Bounds 23 := ⟨by decide, by decide⟩
private instance b31 : ZMod64.Bounds 31 := ⟨by decide, by decide⟩
private instance b71 : ZMod64.Bounds 71 := ⟨by decide, by decide⟩

@[expose]
def main : IO Unit := do
  for n in [11, 12, 13, 15, 18, 22, 24] do
    let f := splitProduct n
    let r3  := @Hex.isGoodPrime f 3 b3
    let r5  := @Hex.isGoodPrime f 5 b5
    let r7  := @Hex.isGoodPrime f 7 b7
    let r11 := @Hex.isGoodPrime f 11 b11
    let r13 := @Hex.isGoodPrime f 13 b13
    let r17 := @Hex.isGoodPrime f 17 b17
    let r19 := @Hex.isGoodPrime f 19 b19
    let r23 := @Hex.isGoodPrime f 23 b23
    let r31 := @Hex.isGoodPrime f 31 b31
    let r71 := @Hex.isGoodPrime f 71 b71
    IO.println s!"n={n}: p=3:{r3} 5:{r5} 7:{r7} 11:{r11} 13:{r13} 17:{r17} 19:{r19} 23:{r23} 31:{r31} 71:{r71}"
